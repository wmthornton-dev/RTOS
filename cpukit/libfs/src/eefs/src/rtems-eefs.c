/*
 * Copyright (c) 2026 Wayne Michael Thornton (WMT) <wmthornton-dev@outlook.com>.  
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * NASA EEPROM Filesystem (EEFS) Driver for RTEMS.
 */

#include <rtems/rtems-eefs.h>
#include <rtems/libio.h>
#include <rtems/score/percpu.h>
#include <string.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>

#define EEFS_MAGIC 0x45454653  /* "EEFS" */
#define EEFS_VERSION 1

/* Forward declarations */
static int eefs_open(
  rtems_libio_t *iop,
  const char *pathname,
  int oflag,
  mode_t mode
);

static int eefs_close(rtems_libio_t *iop);

static ssize_t eefs_read(
  rtems_libio_t *iop,
  void *buffer,
  size_t count
);

static ssize_t eefs_write(
  rtems_libio_t *iop,
  const void *buffer,
  size_t count
);

static off_t eefs_lseek(
  rtems_libio_t *iop,
  off_t offset,
  int whence
);

static int eefs_ftruncate(
  rtems_libio_t *iop,
  off_t length
);

static int eefs_fstat(
  const rtems_filesystem_location_info_t *loc,
  struct stat *buf
);

static int eefs_fs_unmount(rtems_filesystem_mount_table_entry_t *mt_entry);

static void eefs_fsunmount(rtems_filesystem_mount_table_entry_t *mt_entry);

static void eefs_eval_path(
  rtems_filesystem_eval_path_context_t *ctx
);

static int eefs_link(
  const rtems_filesystem_location_info_t *parentloc,
  const rtems_filesystem_location_info_t *targetloc,
  const char *name,
  size_t namelen
);

static int eefs_unlink(
  const rtems_filesystem_location_info_t *parentloc,
  const rtems_filesystem_location_info_t *loc
);

static int eefs_rename(
  const rtems_filesystem_location_info_t *oldparentloc,
  const rtems_filesystem_location_info_t *oldloc,
  const rtems_filesystem_location_info_t *newparentloc,
  const char *name,
  size_t namelen
);

/* Filesystem handlers table */
static rtems_filesystem_file_handlers_r eefs_file_handlers __attribute__((unused)) = {
  .open_h = eefs_open,
  .close_h = eefs_close,
  .read_h = eefs_read,
  .write_h = eefs_write,
  .ioctl_h = rtems_filesystem_default_ioctl,
  .lseek_h = eefs_lseek,
  .fstat_h = eefs_fstat,
  .ftruncate_h = eefs_ftruncate,
  .fsync_h = rtems_filesystem_default_fsync_or_fdatasync,
  .fdatasync_h = rtems_filesystem_default_fsync_or_fdatasync,
  .fcntl_h = rtems_filesystem_default_fcntl,
  .kqfilter_h = rtems_filesystem_default_kqfilter,
  .mmap_h = rtems_filesystem_default_mmap,
  .poll_h = rtems_filesystem_default_poll,
  .readv_h = rtems_filesystem_default_readv,
  .writev_h = rtems_filesystem_default_writev
};

/* Filesystem operations table */
static rtems_filesystem_operations_table eefs_ops = {
  .lock_h = rtems_filesystem_default_lock,
  .unlock_h = rtems_filesystem_default_unlock,
  .eval_path_h = eefs_eval_path,
  .link_h = eefs_link,
  .are_nodes_equal_h = rtems_filesystem_default_are_nodes_equal,
  .mknod_h = rtems_filesystem_default_mknod,
  .rmnod_h = eefs_unlink,
  .fchmod_h = rtems_filesystem_default_fchmod,
  .chown_h = rtems_filesystem_default_chown,
  .clonenod_h = rtems_filesystem_default_clonenode,
  .freenod_h = rtems_filesystem_default_freenode,
  .mount_h = rtems_eefs_initialize,
  .unmount_h = eefs_fs_unmount,
  .fsunmount_me_h = eefs_fsunmount,
  .utimens_h = rtems_filesystem_default_utimens,
  .symlink_h = rtems_filesystem_default_symlink,
  .readlink_h = rtems_filesystem_default_readlink,
  .rename_h = eefs_rename,
  .statvfs_h = rtems_filesystem_default_statvfs
};

/**
 * @brief Calculate CRC32 checksum
 */
uint32_t eefs_crc32(const void *data, size_t length)
{
  const uint8_t *bytes = (const uint8_t *)data;
  uint32_t crc = 0xFFFFFFFF;
  size_t i;
  int j;

  for (i = 0; i < length; i++) {
    crc ^= bytes[i];
    for (j = 0; j < 8; j++) {
      crc = (crc >> 1) ^ (0xEDB88320 & (-(crc & 1)));
    }
  }

  return ~crc;
}

/**
 * @brief Read from EEPROM device
 */
static int eefs_device_read(
  eefs_mount_t *mount,
  uint32_t offset,
  void *buffer,
  size_t length
)
{
  off_t result;
  ssize_t bytes_read;

  if (mount == NULL || buffer == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  result = lseek(mount->device_fd, offset, SEEK_SET);
  if (result == (off_t)-1) {
    return EEFS_ERROR_EEPROM_ERROR;
  }

  bytes_read = read(mount->device_fd, buffer, length);
  if (bytes_read != (ssize_t)length) {
    return EEFS_ERROR_EEPROM_ERROR;
  }

  return EEFS_SUCCESS;
}

/**
 * @brief Write to EEPROM device
 */
static int eefs_device_write(
  eefs_mount_t *mount,
  uint32_t offset,
  const void *buffer,
  size_t length
)
{
  off_t result;
  ssize_t bytes_written;

  if (mount == NULL || buffer == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  result = lseek(mount->device_fd, offset, SEEK_SET);
  if (result == (off_t)-1) {
    return EEFS_ERROR_EEPROM_ERROR;
  }

  bytes_written = write(mount->device_fd, buffer, length);
  if (bytes_written != (ssize_t)length) {
    return EEFS_ERROR_EEPROM_ERROR;
  }

  return EEFS_SUCCESS;
}

/**
 * @brief Find free inode
 */
static int eefs_find_free_inode(eefs_mount_t *mount)
{
  uint32_t i;

  for (i = 0; i < mount->superblock.total_inodes; i++) {
    if (!mount->inode_table[i].in_use) {
      return (int)i;
    }
  }

  return EEFS_ERROR_NO_FREE_INODES;
}

/**
 * @brief Find inode by name
 */
static int eefs_find_inode(eefs_mount_t *mount, const char *name)
{
  uint32_t i;

  if (mount == NULL || name == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  for (i = 0; i < mount->superblock.total_inodes; i++) {
    if (mount->inode_table[i].in_use &&
        strcmp(mount->inode_table[i].name, name) == 0) {
      return (int)i;
    }
  }

  return EEFS_ERROR_FILE_NOT_FOUND;
}

/**
 * @brief Allocate blocks for file
 */
static int eefs_allocate_blocks(
  eefs_mount_t *mount,
  uint32_t num_blocks,
  uint32_t *start_block
)
{
  uint32_t i;
  uint32_t consecutive = 0;
  uint32_t first_block = 0;

  if (num_blocks > mount->superblock.free_blocks) {
    return EEFS_ERROR_NO_FREE_BLOCKS;
  }

  /* Find consecutive free blocks */
  for (i = mount->superblock.data_start_block; 
       i < mount->superblock.total_blocks; i++) {
    if (mount->block_bitmap[i] == 0) {
      if (consecutive == 0) {
        first_block = i;
      }
      consecutive++;
      
      if (consecutive == num_blocks) {
        *start_block = first_block;
        /* Mark blocks as used */
        for (uint32_t j = first_block; j < first_block + num_blocks; j++) {
          mount->block_bitmap[j] = 1;
        }
        mount->superblock.free_blocks -= num_blocks;
        return EEFS_SUCCESS;
      }
    } else {
      consecutive = 0;
    }
  }

  return EEFS_ERROR_NO_FREE_BLOCKS;
}

/**
 * @brief Free blocks
 */
static void eefs_free_blocks(
  eefs_mount_t *mount,
  uint32_t start_block,
  uint32_t num_blocks
)
{
  uint32_t i;

  for (i = start_block; i < start_block + num_blocks; i++) {
    if (i < mount->superblock.total_blocks) {
      mount->block_bitmap[i] = 0;
      mount->superblock.free_blocks++;
    }
  }
}

/**
 * @brief Open file operation
 */
static int eefs_open(
  rtems_libio_t *iop,
  const char *pathname,
  int oflag,
  mode_t mode
)
{
  eefs_mount_t *mount;
  eefs_file_desc_t *file_desc;
  int inode_index;
  rtems_status_code sc;

  (void)mode;

  mount = (eefs_mount_t *)iop->pathinfo.mt_entry->fs_info;
  if (mount == NULL) {
    errno = EINVAL;
    return -1;
  }

  sc = rtems_semaphore_obtain(mount->mutex, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  if (sc != RTEMS_SUCCESSFUL) {
    errno = EIO;
    return -1;
  }

  /* Find or create inode */
  inode_index = eefs_find_inode(mount, pathname);
  
  if (inode_index < 0 && (oflag & O_CREAT)) {
    /* Create new file */
    inode_index = eefs_find_free_inode(mount);
    if (inode_index < 0) {
      rtems_semaphore_release(mount->mutex);
      errno = ENOSPC;
      return -1;
    }

    strncpy(mount->inode_table[inode_index].name, pathname,
            EEFS_MAX_FILENAME_LENGTH - 1);
    mount->inode_table[inode_index].name[EEFS_MAX_FILENAME_LENGTH - 1] = '\0';
    mount->inode_table[inode_index].size = 0;
    mount->inode_table[inode_index].start_block = 0;
    mount->inode_table[inode_index].attributes = EEFS_ATTRIBUTE_NONE;
    mount->inode_table[inode_index].in_use = true;
    mount->inode_table[inode_index].creation_time = time(NULL);
    mount->inode_table[inode_index].modification_time = time(NULL);
  } else if (inode_index < 0) {
    rtems_semaphore_release(mount->mutex);
    errno = ENOENT;
    return -1;
  }

  /* Allocate file descriptor */
  file_desc = (eefs_file_desc_t *)malloc(sizeof(eefs_file_desc_t));
  if (file_desc == NULL) {
    rtems_semaphore_release(mount->mutex);
    errno = ENOMEM;
    return -1;
  }

  file_desc->magic = EEFS_FILE_DESCRIPTOR_MAGIC;
  file_desc->mount = mount;
  file_desc->inode_index = (uint32_t)inode_index;
  file_desc->current_position = 0;
  file_desc->flags = oflag;
  file_desc->is_open = true;

  iop->data1 = file_desc;

  rtems_semaphore_release(mount->mutex);

  return 0;
}

/**
 * @brief Close file operation
 */
static int eefs_close(rtems_libio_t *iop)
{
  eefs_file_desc_t *file_desc;

  file_desc = (eefs_file_desc_t *)iop->data1;
  if (file_desc != NULL && file_desc->magic == EEFS_FILE_DESCRIPTOR_MAGIC) {
    file_desc->is_open = false;
    free(file_desc);
    iop->data1 = NULL;
  }

  return 0;
}

/**
 * @brief Read file operation
 */
static ssize_t eefs_read(
  rtems_libio_t *iop,
  void *buffer,
  size_t count
)
{
  eefs_file_desc_t *file_desc;
  eefs_mount_t *mount;
  eefs_inode_t *inode;
  size_t bytes_to_read;
  size_t bytes_read = 0;
  uint32_t block_offset;
  int result;

  file_desc = (eefs_file_desc_t *)iop->data1;
  if (file_desc == NULL || file_desc->magic != EEFS_FILE_DESCRIPTOR_MAGIC) {
    errno = EBADF;
    return -1;
  }

  mount = file_desc->mount;
  inode = &mount->inode_table[file_desc->inode_index];

  if (file_desc->current_position >= inode->size) {
    return 0;
  }

  bytes_to_read = count;
  if (file_desc->current_position + bytes_to_read > inode->size) {
    bytes_to_read = inode->size - file_desc->current_position;
  }

  block_offset = inode->start_block * mount->superblock.block_size +
                 file_desc->current_position;

  result = eefs_device_read(mount, block_offset, buffer, bytes_to_read);
  if (result != EEFS_SUCCESS) {
    errno = EIO;
    return -1;
  }

  bytes_read = bytes_to_read;
  file_desc->current_position += bytes_read;

  return (ssize_t)bytes_read;
}

/**
 * @brief Write file operation
 */
static ssize_t eefs_write(
  rtems_libio_t *iop,
  const void *buffer,
  size_t count
)
{
  eefs_file_desc_t *file_desc;
  eefs_mount_t *mount;
  eefs_inode_t *inode;
  uint32_t block_offset;
  uint32_t new_blocks_needed;
  int result;

  file_desc = (eefs_file_desc_t *)iop->data1;
  if (file_desc == NULL || file_desc->magic != EEFS_FILE_DESCRIPTOR_MAGIC) {
    errno = EBADF;
    return -1;
  }

  mount = file_desc->mount;
  inode = &mount->inode_table[file_desc->inode_index];

  /* Check if we need to allocate more blocks */
  if (file_desc->current_position + count > 
      inode->size + mount->superblock.block_size) {
    new_blocks_needed = ((file_desc->current_position + count) /
                         mount->superblock.block_size) + 1;
    
    if (inode->start_block == 0) {
      result = eefs_allocate_blocks(mount, new_blocks_needed,
                                    &inode->start_block);
      if (result != EEFS_SUCCESS) {
        errno = ENOSPC;
        return -1;
      }
    }
  }

  block_offset = inode->start_block * mount->superblock.block_size +
                 file_desc->current_position;

  result = eefs_device_write(mount, block_offset, buffer, count);
  if (result != EEFS_SUCCESS) {
    errno = EIO;
    return -1;
  }

  file_desc->current_position += count;
  if (file_desc->current_position > inode->size) {
    inode->size = file_desc->current_position;
    inode->modification_time = time(NULL);
  }

  return (ssize_t)count;
}

/**
 * @brief Seek file operation
 */
static off_t eefs_lseek(
  rtems_libio_t *iop,
  off_t offset,
  int whence
)
{
  eefs_file_desc_t *file_desc;
  eefs_inode_t *inode;
  off_t new_position;

  file_desc = (eefs_file_desc_t *)iop->data1;
  if (file_desc == NULL || file_desc->magic != EEFS_FILE_DESCRIPTOR_MAGIC) {
    errno = EBADF;
    return -1;
  }

  inode = &file_desc->mount->inode_table[file_desc->inode_index];

  switch (whence) {
    case SEEK_SET:
      new_position = offset;
      break;
    case SEEK_CUR:
      new_position = (off_t)file_desc->current_position + offset;
      break;
    case SEEK_END:
      new_position = (off_t)inode->size + offset;
      break;
    default:
      errno = EINVAL;
      return -1;
  }

  if (new_position < 0 || new_position > (off_t)inode->size) {
    errno = EINVAL;
    return -1;
  }

  file_desc->current_position = (uint32_t)new_position;
  return new_position;
}

/**
 * @brief Truncate file operation
 */
static int eefs_ftruncate(
  rtems_libio_t *iop,
  off_t length
)
{
  eefs_file_desc_t *file_desc;
  eefs_inode_t *inode;

  file_desc = (eefs_file_desc_t *)iop->data1;
  if (file_desc == NULL || file_desc->magic != EEFS_FILE_DESCRIPTOR_MAGIC) {
    errno = EBADF;
    return -1;
  }

  inode = &file_desc->mount->inode_table[file_desc->inode_index];

  if (length < 0) {
    errno = EINVAL;
    return -1;
  }

  inode->size = (uint32_t)length;
  inode->modification_time = time(NULL);

  return 0;
}

/**
 * @brief Get file status
 */
static int eefs_fstat(
  const rtems_filesystem_location_info_t *loc,
  struct stat *buf
)
{
  eefs_mount_t *mount;
  eefs_inode_t *inode;
  int inode_index;

  mount = (eefs_mount_t *)loc->mt_entry->fs_info;
  inode_index = eefs_find_inode(mount, (const char *)loc->node_access);

  if (inode_index < 0) {
    errno = ENOENT;
    return -1;
  }

  inode = &mount->inode_table[inode_index];

  memset(buf, 0, sizeof(struct stat));
  buf->st_mode = S_IFREG | S_IRUSR | S_IWUSR;
  buf->st_nlink = 1;
  buf->st_size = (off_t)inode->size;
  buf->st_blksize = (blksize_t)mount->superblock.block_size;
  buf->st_blocks = (blkcnt_t)((inode->size + mount->superblock.block_size - 1) /
                              mount->superblock.block_size);
  buf->st_ctime = inode->creation_time;
  buf->st_mtime = inode->modification_time;

  return 0;
}

/**
 * @brief Filesystem unmount operation
 */
static void eefs_fsunmount(rtems_filesystem_mount_table_entry_t *mt_entry)
{
  eefs_mount_t *mount;

  mount = (eefs_mount_t *)mt_entry->fs_info;
  if (mount != NULL) {
    if (mount->device_fd >= 0) {
      close(mount->device_fd);
    }
    if (mount->inode_table != NULL) {
      free(mount->inode_table);
    }
    if (mount->block_bitmap != NULL) {
      free(mount->block_bitmap);
    }
    if (mount->mutex != RTEMS_ID_NONE) {
      rtems_semaphore_delete(mount->mutex);
    }
    free(mount);
  }
}

/**
 * @brief Mount filesystem (filesystem operation)
 */
/**
 * @brief Unmount filesystem (filesystem operation)
 */
static int eefs_fs_unmount(
  rtems_filesystem_mount_table_entry_t *mt_entry
)
{
  (void)mt_entry;
  
  return 0;
}

/**
 * @brief Evaluate path operation
 */
static void eefs_eval_path(
  rtems_filesystem_eval_path_context_t *ctx
)
{
  /* Simplified path evaluation */
  rtems_filesystem_default_eval_path(ctx);
}

/**
 * @brief Link operation (not supported)
 */
static int eefs_link(
  const rtems_filesystem_location_info_t *parentloc,
  const rtems_filesystem_location_info_t *targetloc,
  const char *name,
  size_t namelen
)
{
  (void)parentloc;
  (void)targetloc;
  (void)name;
  (void)namelen;
  
  errno = ENOTSUP;
  return -1;
}

/**
 * @brief Unlink operation
 */
static int eefs_unlink(
  const rtems_filesystem_location_info_t *parentloc,
  const rtems_filesystem_location_info_t *loc
)
{
  eefs_mount_t *mount;
  int inode_index;
  eefs_inode_t *inode;

  (void)parentloc;

  mount = (eefs_mount_t *)loc->mt_entry->fs_info;
  inode_index = eefs_find_inode(mount, (const char *)loc->node_access);

  if (inode_index < 0) {
    errno = ENOENT;
    return -1;
  }

  inode = &mount->inode_table[inode_index];
  
  /* Free blocks */
  if (inode->start_block > 0) {
    uint32_t num_blocks = (inode->size + mount->superblock.block_size - 1) /
                          mount->superblock.block_size;
    eefs_free_blocks(mount, inode->start_block, num_blocks);
  }

  /* Clear inode */
  memset(inode, 0, sizeof(eefs_inode_t));
  inode->in_use = false;

  return 0;
}

/**
 * @brief Rename operation
 */
static int eefs_rename(
  const rtems_filesystem_location_info_t *oldparentloc,
  const rtems_filesystem_location_info_t *oldloc,
  const rtems_filesystem_location_info_t *newparentloc,
  const char *name,
  size_t namelen
)
{
  eefs_mount_t *mount;
  int inode_index;
  eefs_inode_t *inode;

  (void)oldparentloc;
  (void)newparentloc;

  mount = (eefs_mount_t *)oldloc->mt_entry->fs_info;
  inode_index = eefs_find_inode(mount, (const char *)oldloc->node_access);

  if (inode_index < 0) {
    errno = ENOENT;
    return -1;
  }

  if (namelen >= EEFS_MAX_FILENAME_LENGTH) {
    errno = ENAMETOOLONG;
    return -1;
  }

  inode = &mount->inode_table[inode_index];
  strncpy(inode->name, name, namelen);
  inode->name[namelen] = '\0';

  return 0;
}

/**
 * @brief Initialize RTEMS EEPROM filesystem driver
 *
 * This function serves as the mount function for the EEFS filesystem.
 * It is called when mounting an EEFS filesystem and is responsible for
 * setting up the filesystem operations table for the mount entry.
 *
 * @param[in,out] mt_entry The mount table entry to initialize
 * @param[in] data Optional mount-specific data (currently unused)
 *
 * @retval 0 Successful operation
 * @retval -1 Error occurred (errno set appropriately)
 */
int rtems_eefs_initialize(
  rtems_filesystem_mount_table_entry_t *mt_entry,
  const void *data
)
{
  (void)data;
  
  mt_entry->ops = &eefs_ops;
  
  return 0;
}

/**
 * @brief Format EEPROM device with EEFS
 */
int eefs_format(
  const char *device_path,
  uint32_t total_size,
  uint32_t max_files
)
{
  eefs_superblock_t superblock;
  int fd;
  int result;

  if (device_path == NULL || total_size == 0 || max_files == 0) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  fd = open(device_path, O_RDWR);
  if (fd < 0) {
    return EEFS_ERROR_EEPROM_ERROR;
  }

  /* Initialize superblock */
  memset(&superblock, 0, sizeof(eefs_superblock_t));
  superblock.magic = EEFS_MAGIC;
  superblock.version = EEFS_VERSION;
  superblock.block_size = EEFS_BLOCK_SIZE;
  superblock.total_blocks = total_size / EEFS_BLOCK_SIZE;
  superblock.total_inodes = max_files;
  superblock.free_inodes = max_files;
  superblock.inode_table_block = 1;
  superblock.data_start_block = 1 + (max_files * sizeof(eefs_inode_t)) /
                                 EEFS_BLOCK_SIZE + 1;
  superblock.free_blocks = superblock.total_blocks -
                           superblock.data_start_block;
  superblock.crc = eefs_crc32(&superblock, sizeof(eefs_superblock_t) - 4);

  /* Write superblock */
  result = write(fd, &superblock, sizeof(eefs_superblock_t));
  if (result != sizeof(eefs_superblock_t)) {
    close(fd);
    return EEFS_ERROR_EEPROM_ERROR;
  }

  close(fd);
  return EEFS_SUCCESS;
}

/**
 * @brief Mount EEPROM filesystem
 */
int eefs_mount(
  const char *device_path,
  const char *mount_point
)
{
  eefs_mount_t *mount;
  rtems_status_code sc;
  int result;

  if (device_path == NULL || mount_point == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  /* Allocate mount structure */
  mount = (eefs_mount_t *)calloc(1, sizeof(eefs_mount_t));
  if (mount == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  /* Open device */
  mount->device_fd = open(device_path, O_RDWR);
  if (mount->device_fd < 0) {
    free(mount);
    return EEFS_ERROR_EEPROM_ERROR;
  }

  /* Read superblock */
  result = eefs_device_read(mount, 0, &mount->superblock,
                            sizeof(eefs_superblock_t));
  if (result != EEFS_SUCCESS) {
    close(mount->device_fd);
    free(mount);
    return result;
  }

  /* Verify superblock */
  if (mount->superblock.magic != EEFS_MAGIC) {
    close(mount->device_fd);
    free(mount);
    return EEFS_ERROR_EEPROM_ERROR;
  }

  /* Allocate inode table */
  mount->inode_table = (eefs_inode_t *)calloc(mount->superblock.total_inodes,
                                              sizeof(eefs_inode_t));
  if (mount->inode_table == NULL) {
    close(mount->device_fd);
    free(mount);
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  /* Allocate block bitmap */
  mount->block_bitmap = (uint8_t *)calloc(mount->superblock.total_blocks, 1);
  if (mount->block_bitmap == NULL) {
    free(mount->inode_table);
    close(mount->device_fd);
    free(mount);
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  /* Create mutex for thread safety */
  sc = rtems_semaphore_create(
    rtems_build_name('E', 'E', 'F', 'S'),
    1,
    RTEMS_BINARY_SEMAPHORE | RTEMS_PRIORITY | RTEMS_INHERIT_PRIORITY,
    0,
    &mount->mutex
  );

  if (sc != RTEMS_SUCCESSFUL) {
    free(mount->block_bitmap);
    free(mount->inode_table);
    close(mount->device_fd);
    free(mount);
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  mount->device_path = device_path;
  mount->mounted = true;

  (void)mount_point;

  return EEFS_SUCCESS;
}

/**
 * @brief Unmount EEPROM filesystem
 */
int eefs_unmount(const char *mount_point)
{
  if (mount_point == NULL) {
    return EEFS_ERROR_INVALID_PARAMETER;
  }

  (void)mount_point;

  return EEFS_SUCCESS;
}
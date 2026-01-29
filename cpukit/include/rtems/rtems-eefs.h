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
 * NASA EEPROM Filesystem (EEFS) Driver Header for RTEMS.
 */

#ifndef _RTEMS_EEFS_h
#define _RTEMS_EEFS_h

#include <rtems.h>
#include <rtems/libio.h>
#include <rtems/score/thread.h>
#include <sys/types.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/**
 * @defgroup EEFS EEPROM Filesystem Driver
 * @ingroup FileSystemTypesAndMount
 * @brief NASA EEPROM Filesystem for RTEMS
 */
/**@{**/

/* Configuration constants */
#define EEFS_MAX_FILENAME_LENGTH 20
#define EEFS_MAX_OPEN_FILES 10
#define EEFS_BLOCK_SIZE 512
#define EEFS_INODE_OVERHEAD 32
#define EEFS_FILE_DESCRIPTOR_MAGIC 0xEEF5

/* File attributes */
#define EEFS_ATTRIBUTE_NONE 0x00
#define EEFS_ATTRIBUTE_READONLY 0x01
#define EEFS_ATTRIBUTE_HIDDEN 0x02

/* Return codes */
#define EEFS_SUCCESS 0
#define EEFS_ERROR_NO_FREE_INODES -1
#define EEFS_ERROR_FILE_NOT_FOUND -2
#define EEFS_ERROR_INVALID_PARAMETER -3
#define EEFS_ERROR_NO_FREE_BLOCKS -4
#define EEFS_ERROR_EEPROM_ERROR -5
#define EEFS_ERROR_FILE_OPEN -6

/**
 * @brief EEPROM Filesystem inode structure
 */
typedef struct {
  char name[EEFS_MAX_FILENAME_LENGTH];
  uint32_t size;
  uint32_t start_block;
  uint32_t crc;
  uint8_t attributes;
  bool in_use;
  time_t creation_time;
  time_t modification_time;
} eefs_inode_t;

/**
 * @brief EEPROM Filesystem superblock structure
 */
typedef struct {
  uint32_t magic;
  uint32_t version;
  uint32_t total_blocks;
  uint32_t free_blocks;
  uint32_t total_inodes;
  uint32_t free_inodes;
  uint32_t block_size;
  uint32_t inode_table_block;
  uint32_t data_start_block;
  uint32_t crc;
} eefs_superblock_t;

/**
 * @brief EEPROM Filesystem mount table entry
 */
typedef struct {
  eefs_superblock_t superblock;
  eefs_inode_t *inode_table;
  uint8_t *block_bitmap;
  rtems_id mutex;
  const char *device_path;
  int device_fd;
  bool mounted;
} eefs_mount_t;

/**
 * @brief EEPROM Filesystem file descriptor
 */
typedef struct {
  uint32_t magic;
  eefs_mount_t *mount;
  uint32_t inode_index;
  uint32_t current_position;
  int flags;
  bool is_open;
} eefs_file_desc_t;

/**
 * @brief EEPROM device operations structure
 */
typedef struct {
  int (*read)(uint32_t offset, void *buffer, size_t length);
  int (*write)(uint32_t offset, const void *buffer, size_t length);
  int (*erase)(uint32_t offset, size_t length);
} eefs_device_ops_t;

/**
 * @brief Initialize the EEPROM filesystem driver
 *
 * This function is called by the filesystem table during mount operations.
 * It initializes the EEFS filesystem for a mount table entry.
 *
 * @param[in] mt_entry The mount table entry to initialize
 * @param[in] data Optional mount-specific data
 *
 * @retval 0 Successful operation
 * @retval -1 Error occurred (errno set appropriately)
 */
int rtems_eefs_initialize(
  rtems_filesystem_mount_table_entry_t *mt_entry,
  const void *data
);

/**
 * @brief Format an EEPROM device with the EEFS filesystem
 *
 * @param device_path Path to the EEPROM device
 * @param total_size Total size of the EEPROM in bytes
 * @param max_files Maximum number of files supported
 * @return EEFS_SUCCESS on success, error code otherwise
 */
int eefs_format(
  const char *device_path,
  uint32_t total_size,
  uint32_t max_files
);

/**
 * @brief Mount an EEPROM filesystem
 *
 * @param device_path Path to the EEPROM device
 * @param mount_point Path where filesystem will be mounted
 * @return EEFS_SUCCESS on success, error code otherwise
 */
int eefs_mount(
  const char *device_path,
  const char *mount_point
);

/**
 * @brief Unmount an EEPROM filesystem
 *
 * @param mount_point Path where filesystem is mounted
 * @return EEFS_SUCCESS on success, error code otherwise
 */
int eefs_unmount(const char *mount_point);

/**
 * @brief Calculate CRC32 for data integrity
 *
 * @param data Pointer to data buffer
 * @param length Length of data in bytes
 * @return CRC32 value
 */
uint32_t eefs_crc32(const void *data, size_t length);

/**@}**/


#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* _RTEMS_EEFS_h */
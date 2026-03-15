/* SPDX-License-Identifier: BSD-2-Clause */

/**
 *      @file
 *
 *      @brief Age Verification API
 *
 *      This include file contains all the constants and structures associated
 *      with the Age Verification API.
 */

 /* Copyright (C) 2026 Wayne Michael Thornton (WMT) <wmthornton-dev@outlook.com>
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
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef _RTEMS_AGE_VERIFY_H
#define _RTEMS_AGE_VERIFY_H

#include <rtems.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Age Verification Brackets.
 *
 * These age brackets are mandatory but can be changed as needed 
 * to comply with the laws of different regions. Changes to the
 * rtems_age_set_bracket logic in age_verify.c would be needed if 
 * this enum is modified.
 */
typedef enum {
  AGE_UNDER_13 = 0, /* Under 13, U.S. Federal COPPA applies (no tracking) */
  AGE_13_TO_15 = 1, /* Under 16, High-Privacy Minor (no addictive features) */
  AGE_16_TO_17 = 2, /* Under 18, Older Minor (no legally binding EULA/contracts) */
  AGE_18_PLUS  = 3
} rtems_age_bracket;

/**
 * @brief Sets the system age verification bracket.
 *
 * Called by the OS or application setup process to initialize the 
 * verification signal. This function enforces a write-once lock.
 *
 * @param bracket The verified age bracket to store in the system.
 *
 * @retval RTEMS_SUCCESSFUL The age bracket was successfully locked in.
 * @retval RTEMS_INVALID_NUMBER The provided bracket is outside the valid enum range.
 * @retval RTEMS_NOT_CONFIGURED The age bracket has already been set and is locked.
 */
rtems_status_code rtems_age_set_bracket(rtems_age_bracket bracket);

/**
 * @brief Retrieves the system age verification signal.
 *
 * Called by applications to check the age signal. This function will 
 * validate the internal memory canaries before returning the data.
 *
 * @return Returns the stored age bracket as a uint8_t signal.
 */
uint8_t rtems_age_get_signal(void);

#ifdef __cplusplus
}
#endif

#endif /* _RTEMS_AGE_VERIFY_H */
/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @brief Age Verification API Implementation
 *
 * This source file contains the bounds-checked implementation of the 
 * state-mandated Age Verification API.
 */

/*
 * Copyright (C) 2026 Wayne Michael Thornton (WMT) <wmthornton-dev@outlook.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
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

#include <rtems/age_verify.h>
#include <rtems/fatal.h>
#include <stdbool.h>

#define AGE_GUARD_PATTERN 0xDEADBEEF
#define AGE_UNINITIALIZED 0xFFFFFFFF

/**
 * @brief Protected Age Data Structure.
 *
 * This structure is designed to be resistant to tampering and memory corruption. The 
 * guard values should help detect any attempts to overwrite the age bracket and implements 
 * encapsulation to guarantee memory layout and prevent compiler padding issues. I'm 
 * not even really sure if this is necessary, but it adds an extra layer of safety and 
 * integrity to the system and complies with the law in a more robust way.
 */
typedef struct {
    uint32_t lower_guard;
    uint32_t age_bracket; 
    uint32_t upper_guard;
} rtems_age_protected_t;

static rtems_age_protected_t _Age_Data = {
    .lower_guard = AGE_GUARD_PATTERN,
    .age_bracket = AGE_UNINITIALIZED,
    .upper_guard = AGE_GUARD_PATTERN
};

static bool _Age_Locked = false;

rtems_status_code rtems_age_set_bracket(rtems_age_bracket bracket) {
    if (bracket > AGE_18_PLUS) return RTEMS_INVALID_NUMBER;
    if (_Age_Locked) return RTEMS_NOT_CONFIGURED;

    _Age_Data.age_bracket = (uint32_t)bracket;
    _Age_Locked = true;
    return RTEMS_SUCCESSFUL;
}

/* Verify the integrity of the age data before returning it. 
 * If the guard values have been tampered with, this likely 
 * indicates memory corruption or a tampering attempt.
 */
uint8_t rtems_age_get_signal(void) {
    
    if (_Age_Data.lower_guard != AGE_GUARD_PATTERN || 
        _Age_Data.upper_guard != AGE_GUARD_PATTERN) {
        
        rtems_fatal(RTEMS_FATAL_SOURCE_STACK_CHECKER, 0xBAD1D);
    }

    return (uint8_t)_Age_Data.age_bracket;
}
/* SPDX-License-Identifier: BSD-2-Clause */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/test.h>
#include <rtems/test-info.h>
#include <rtems/age_verify.h>
#include <stdio.h>
#include <stdlib.h>

const char rtems_test_name[] = "AGE_VERIFY01";

static void Init(rtems_task_argument arg) {
    rtems_status_code sc;
    uint8_t signal;

    /* Suppress the unused parameter warning treated as an error by cc1 */
    (void) arg; 

    printf("\n\n*** BEGIN OF TEST %s ***\n", rtems_test_name);

    printf("1. Testing out-of-bounds bracket input...\n");
    sc = rtems_age_set_bracket(5); /* 5 is outside the enum */
    if (sc == RTEMS_INVALID_NUMBER) {
        printf("   PASS: Invalid bracket correctly rejected.\n");
    } else {
        printf("   FAIL: Invalid bracket accepted! Status: %d\n", sc);
    }

    printf("2. Testing valid bracket assignment (AGE_16_TO_17)...\n");
    sc = rtems_age_set_bracket(AGE_16_TO_17);
    if (sc == RTEMS_SUCCESSFUL) {
        printf("   PASS: Valid bracket successfully set.\n");
    } else {
        printf("   FAIL: Could not set valid bracket! Status: %d\n", sc);
    }

    printf("3. Testing API lock mechanism...\n");
    sc = rtems_age_set_bracket(AGE_18_PLUS);
    if (sc == RTEMS_NOT_CONFIGURED) {
        printf("   PASS: API correctly locked after initial configuration.\n");
    } else {
        printf("   FAIL: API allowed overwriting the protected bracket!\n");
    }

    printf("4. Testing signal retrieval and memory read...\n");
    signal = rtems_age_get_signal();
    if (signal == AGE_16_TO_17) {
        printf("   PASS: Retrieved correct bracket signal (%d).\n", signal);
        printf("   PASS: Canary guards are intact.\n");
    } else {
        printf("   FAIL: Retrieved incorrect signal: %d\n", signal);
    }

    printf("*** END OF TEST %s ***\n\n", rtems_test_name);
    rtems_test_exit(0);
}

/* RTEMS Configuration for Test Application */
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER
#define CONFIGURE_MAXIMUM_TASKS 1
#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION
#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_INIT
#include <rtems/confdefs.h>
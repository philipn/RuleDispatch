from unittest import TestSuite, TestCase, makeSuite

def test_suite():

    from dispatch.tests import test_dispatch, test_parsing

    tests = [
        test_dispatch.test_suite(),
        test_parsing.test_suite(),
    ]

    return TestSuite(
        tests
    )


#!/bin/env groovy

node {
    checkout(
        poll: false,
        scm: [
            $class: 'GitSCM',
            branches: scm.branches,
            extensions: scm.extensions + [[$class: 'CleanBeforeCheckout'], [$class: 'CloneOption', depth: 1, noTags: true, shallow: true]],
            userRemoteConfigs: scm.userRemoteConfigs
        ]
    )

    stage ("Load CI Scripts") {
        dir ("dlang/ci") {
            git "https://github.com/dlang-test/ci.git"
        }
    }

    load "dlang/ci/pipeline.groovy"
}

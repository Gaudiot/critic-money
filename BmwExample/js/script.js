var module = angular.module('phone', ['xeditable'])
  .controller('pCtrl', function($scope) {

    bms.observe("formula", {
      formulas: ["db", "active"],
      translate: true,
      trigger: function(values) {
        $scope.db = values[0];
        $scope.active = values[1];
      }
    });

    $scope.isActive = function(name) {
      return $scope.active.indexOf(name) > -1;
    }

    $scope.update = function(name, nr, type) {
      bms.executeEvent({
        name: "update",
        predicate: 'name="' + name + '" & nr=' + nr
      });
    };

  });

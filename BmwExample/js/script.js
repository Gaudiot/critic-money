var module = angular.module('phone', ['xeditable'])
  .controller('pCtrl', function($scope) {

    bms.observe("formula", {
      formulas: ["CLIENTS"],
      translate: true,
      trigger: function(values) {
        $scope.clients = values[0];
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

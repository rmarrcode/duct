datatype User = User(id: int, name: string)
datatype Order = Order(orderId: int, userId: int, amount: int)

datatype UserOrder = UserOrder(userName: string, orderId: int, amount: int)

class DB {
  var users: seq<User>
  var orders: seq<Order>

  constructor(initUsers: seq<User>, initOrders: seq<Order>) {
    users := initUsers;
    orders := initOrders;
  }

  // Returns a sequence of joined results pairing users and their orders
  method JoinUserOrders() returns (result: seq<UserOrder>)
    ensures forall jo :: jo in result ==> exists u :: exists o :: u in users && o in orders && u.id == o.userId && jo.userName == u.name && jo.orderId == o.orderId && jo.amount == o.amount
    ensures forall u :: u in users ==> (forall o :: o in orders && o.userId == u.id ==> exists jo :: jo in result && jo.userName == u.name && jo.orderId == o.orderId)
  {
    var joined := [];
    foreach u in users {
      foreach o in orders {
        if o.userId == u.id {
          joined := joined + [UserOrder(u.name, o.orderId, o.amount)];
        }
      }
    }
    return joined;
  }
}

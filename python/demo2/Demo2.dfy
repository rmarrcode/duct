module {:extern "M"} M {
  class C {
    static method p() {
      print "Hello, World\n";
    }
  }
}

method Main() {
  // This ensures the module gets compiled
}

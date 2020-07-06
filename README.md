# Beating the CAP theorem: the epidemic register

The CAP theorem states that distributed data structures cannot have
all three of the following properties:

* consistency
* availability
* partition tolerance

But the CAP theorem is a general result, it doesn't say anything about whether
any particular data structure can have all three properties.

It turns out that there is a data structure that has all three properties: 
the *epidemic register*.

This post uses that register as an example to explain the CAP theorem, as
well as illustrate how to do some formal specifying use TLA+ and Alloy.

A lot of this is based on Sebastian Burckhardt's excellent (free!) book 
[Principles of Eventual Consistency][PoEC]

# What's a register?


A register is a data structure that supports two operation:

* write value
* read value

A register behaves like a variable in a programming language. It's
such a simple data structure, that you may have not even heard
of it unless you've studied computer architecture or distributed systems.

Computer architects care about registers because CPUs have registers
inside them: you load data from memory into registers, and then
the instructions operate on the data inside of the registers.

Distributed systems researchers care about registers because, even though
they are such a simple data structure, even the simplest data structure
is very complex when implemented in a distributed system!


# What does the CAP theorem really mean?

We need a formal definition of the CAP theorem.

## Consistency

Sequential consistency.

Similar to serializability for transactions.

Note that this is weaker than linearizability.

## Availability

Operations can't block

## Partition tolerance

An arbitrary amount of messages may be lost


# What is an epidemic register?

Here's an implementation of an epidemic register from Burckhardt's [Principles
of Eventual Consistency][PoEC] (Fig 1.2, p14), in pseudocode:

```
protocol EpidemicRegister {

  struct Timestamp(number: nat; pid: nat) ;
  function lessthan(Timestamp(n1,pid1), Timestamp(n2,pid2)) {
    return (n1 < n2) ∨ (n1 == n2 ∧ pid1 < pid2) ;
}

  message Latest(val: Value, t: Timestamp) : dontforge, eventualindirect

  role Peer(pid: { 0 .. N }) {

    var current: Value := undef ;
    var written: Timestamp := Timestamp(0,pid) ;

    operation read() {
      return current;
    }
    operation write(val: Value) {
      current := val ;
      written := Timestamp(written.number + 1,pid) ;
      return ok ;
    }

  periodically {
    send Latest(current, written) ;
  }

  receive Latest(val,ts) {
    if (written.lessthan(ts)) {
      current := val ;
      written := ts;
      }
    }
  }
}

```

# TLA+

See [epidemic.tla][epidemic.tla] for the TLA+/PlusCal model.

There's a refinement that shows that this implementation is a sequentially consistent implementation
of the spec [register.tla][register.tla].

# Alloy


[PoEC]: https://www.microsoft.com/en-us/research/publication/principles-of-eventual-consistency/

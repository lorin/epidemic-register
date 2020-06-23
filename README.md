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
[Principles of Eventual Consistency](https://www.microsoft.com/en-us/research/publication/principles-of-eventual-consistency/).


# What does the CAP theorem really mean?

We need a formal definition of the CAP theorem.

## Consistency

Sequential consistency.

Similar to serializability for transactiosn

## Availability

Operations can't block

## Partition tolerance

An arbitrary amount of messages may be lost


----
### *.abc: the AbC specifications
### *.c: the generated C files

## Or-Bit

Each component has an attribute i standing for input bit, and o standing for output. Components must produce the "or" bit of all other input bits.

## Max-Elem
Each component has a value n and a flag s. After interactions, there is only one component remains s has its n as the maximum value.

## Dance
Each component is given a role, either Leader or Follower. Determine if there are more leaders than followers.

## Philosopher (Phil2)
Each philosopher has an opinion o (high, low) and a physical condition c (strong, weak), debating on a topic:
1. Phils with the same o do not debate
2. Two Phils with different o debate
- the one with better c convinces the other to change his opinion
- if same o, they both get weak and the one with low opinion turns to high opinion.

Determine if there is a majority of a high opinion

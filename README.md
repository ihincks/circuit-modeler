# circuit-modeler
Tools for working with lumped element electrical circuits in *Mathematica*.

## Requirements

Tested with *Mathematica* 10.0.2. Should work with *Mathematica* 9 and higher, but is untested.

## Installation

Open the notebook `Install.nb` and follow the directions there.

## Features

This library is in many ways still very basic; it was an overkill project to spare some people from having to do some easy calculations by hand. Still, it is very useful if you want to do any of the following easily and symbolically:

 - Express circuits as abitrary graphs of lumped elements, much like in SPICE, however, component values can be symbolic.
 - Apply KirchoffsLaws to circuit graphs to get circuit equations in time or Laplace domain.
 - Compute S (scattering), X, Y of circuits with an arbitrary number of ports. Compute ABCD matrix for two-port devices.
 - Visualize circuit graphs, plot S-parameters, etc.

## License

You are free to use this software, with or without modification, provided that the conditions listed in the LICENSE.txt file are satisfied.

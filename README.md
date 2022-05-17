# gGHS-check
Script to check if a given binary GLS curve is (or not) vulnerable under the gGHS attack

To work with different curves replace 
1. `bK1`
2. `aK1`

The script assumes curves defined over `F_q[u]/(u^2 + u + 1)` where `F_q = F_2[v]/(v^127 + v^63 + 1)`.
Working with different fields implies change on the lists of polynomials `S_F4` and `S_F2`.

## Comments
This scripts corresponds with the [Attacking a Binary GLS Elliptic Curve with magma](https://link.springer.com/chapter/10.1007/978-3-319-22174-8_17)
You can find a public version of the results on my [Master's thesis](https://repositorio.cinvestav.mx/bitstream/handle/cinvestav/2324/SSIT0013703.pdf?sequence=1).

## Credits
Jesus-Javier Chi Dominguez <jesus.dominguez@tii.ae;chidoys@gmail.com>

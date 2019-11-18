# Echidna Algorithms: Algorithms for Elliptic Curves and Higher Dimensional Analogues


This is just a mirror of http://iml.univ-mrs.fr/~kohel/alg/index.html

<table>
  <tr>
    <td width="30%" align="left"><font size=4><b>Echidna Algorithms</b></font></td>
    <td width="30%" align="left"><b>Latest version:</b> <a href="http://iml.univ-mrs.fr/~kohel/alg/echidna-5.0.spkg">echidna-5.0.spkg</a></td>
    <td width="40%" align="left"><b>Previous versions:</b> <a href="http://iml.univ-mrs.fr/~kohel/alg/echidna-4.0.spkg">echidna-4.0.spkg</a></td>
  </tr>
  <tr>
    <td colspan=3><hr noshade size=2></td>
  </tr>
  <tr>
    <td colspan=3>
This is the complete Sage package for Echidna Algorithms, version 5.0 (for Magma V2.19 or higher).
This code is designed for computational and algorithmic research in the arithmetic
of curves, Jacobian, number fields (particularly CM fields), lattices, and algebras,
over a period of many years, including code contributions by and/or the output of
collaborations
with Robert Carls, Pierrick Gaudry, Martine Girard, David Gruenewald, Thomas Houtmann,
Hamish Ivey-Law, J&uuml;rgen Kl&uuml;ners, David Lubicz, Christophe Ritzenthaler,
Benjamin Smith, William Stein, Helena Verrill, Annegret Weng, Geordie Williamson,
and others.
Description of individual packages and some documentation can be found below.<p>

This package is a bzip2'ed tar file of open source
<a href="http://magma.maths.usyd.edu.au">Magma</a> code.

For databases of modular polynomials, defining modular curves and their correspondences,
class polynomials for genus 1 and 2, quaternion algebras, and of Brandt modules and their
decompositions and Hecke algebra structures, consult the page
<a href="http://iml.univ-mrs.fr/~kohel/alg/../dbs/index.html">Echidna Databases</a>
for associated data.<p>

For Magma code development, emacs users may find this customizable
<a href="http://iml.univ-mrs.fr/~kohel/alg/emacs/index.html">magma mode</a> may be of use (version is adapted from an initial
version of William Stein, which was in turn derived from the GNU elisp shell.el).<p>

<b>INSTALLATION:</b>
The tar file expands (tar -xvjf echidna-5.0.spkg) into a directory structure echidna-5.0/[src,dbs].
To avoid the need to modify the path in echidna-5.0/src/System/directory.m,
you should define an ECHIDNA_ROOT environment variable.  For instance in bash,
place:
<p>
export ECHIDNA_ROOT=$HOME/echidna-5.0
<p>
in your .bash_profile.  Now, to automatically load Echidna on startup,
place the following line in your .magmarc file:
<p>
AttachSpec(GetEnv("ECHIDNA_ROOT")*"/src/echidna.spec");
<p>
or call this from Magma.
<p>
<b>BUG REPORTS:</b> Please report any bugs to David Kohel
<a href="mailto:David.Kohel@univ-amu.fr">David.Kohel@univ-amu.fr</a>.
</td>
  </tr>
  <tr>
    <td colspan=3><hr noshade size=2></td>
  </tr>
</table>
<table>
  <tr>
    <td width="40%" align="left"><i>Package Title</i></td>
    <td width="30%" align="left"><i>Documentation</i></td>
    <td width="30%"></td>
  </tr>
  <tr>
    <td><b>Quaternion Algebras</b></td>
    <td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/AlgQuat.pdf">AlgQuat.pdf</a></td>
  </tr>
  <tr>
    <td colspan=3>This is a package for quaternion algebras and their
      orders, with special functionality for quaternion algebras over the
      rationals.</td>
  </tr>
  <tr>
    <td><b>Brandt Modules</b></td>
    <td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/ModBrdt.pdf">ModBrdt.pdf</a></td>
  </tr>
  <tr>
    <td colspan=3>This is a package for working in the free module generated
      by the left ideal classes of a definite quaternion algebra over
      the rationals.</td>
  </tr>
  <tr>
    <td><b>AGM-X<sub>0</sub>(N)</b></td>
    <td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/AGM-X0.pdf">AGM-X0.pdf</a></td>
  </tr>
  <tr>
    <td colspan=3>This is a package for point counting in elliptic curves
       over finite fields of characteristics 2, 3, 5, 7, and 13.
       In a generalization of the p-adic lifting method of Mestre, this
       algorithms uses models for modular curves of genus zero to lift
       CM points p-adically to characteristic zero, and "read off" the
       trace of Frobenius from its action on the space of differentials
       of a parametrized curve. This package complements my Asiacrypt'03
       article "The AGM-X0(N) Heegner point lifting algorithm and
       elliptic curve point counting".
</td>
  </tr>
  <tr>
    <td><b>Picard Groups</b></td>
    <td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/PicCrv.pdf">PicCrv.pdf</a></td>
  </tr>
  <tr>
    <td colspan=3>This is a package for working in the Picard group of
    a curve.  The present implementation forms the Picard group
    of the nonsingular resolution of the input curve.</td>
  </tr>
  <tr>
    <td><b>Singular Cubic Curves</b></td>
    <!--<td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/CrvGrp.pdf">CrvGrp.pdf</a></td>-->
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>This package is an implementation of the group law on
    possibly singular cubic curves, extending the elliptic curve group law
    to this larger class of curves.</td>
  </tr>
  <tr>
    <td><b>Singular Hyperelliptics</b></td>
    <td align="left">
    <!--<td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/JacHypSng.pdf">JacHypSng.pdf</a></td>-->
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>This package implements the generalized Jacobian
    of a singular hyperelliptic curve as described in my preprint
    "Constructive and destructive aspects of torus-based cryptography".
    The file <a href="doc/jachypsng.m">jachypsng.m</a> is sample code
    demonstrating its use for jacobian arithmetic, discrete logarithms,
    and morphisms between jacobians and the multiplicative group as
    described in the preprint.  The package for singular cubic curves
    is also used in this file.</td>
  </tr>
  <tr>
    <td><b>Genus 2 Curve Invariants and Canonical Lifts</b></td>
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>
    This package is a bundle of code for computing with moduli of genus 2 curves, Igusa
    invariants, Rosenhain invariants, and theta null values and their canonical lifts.
    The underlying algorithms represents research with Ritzenthaler, and subsequently
    Gaudry, Houtman, and Weng; with Ben Smith; and with Carls and Lubicz.
    </td>
  </tr>
  <tr>
    <td><b>Jacobians of Genus 2 Curves</b></td>
    <td align="left">
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>
    This package contains code for computing a projective embedding for the Jacobian of
    a genus 2 curve, and its formal group.  This includes code written with Geordie
    Williamson.
    </td>
  </tr>
  <tr>
    <td><b>Hyperelliptic Jacobians</b></td>
    <!--<td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/JacHyp.pdf">JacHyp.pdf</a></td>-->
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>
    Various algorithms for computing endomorphism rings of a hyperelliptic Jacobians and
    simple index calculus relation calculations.
    </td>
  </tr>
  <tr>
    <td><b>Quartic CM Fields</b></td>
    <td align="left">
    <!--<td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/FldCM.pdf">FldCM.pdf</a></td>-->
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>
    Algorithms for quartic CM fields (invariants, reflex fields, real subfields, etc.).
    </td>
  </tr>
  <tr>
    <td><b>Genus 3 Curve Invariants</b></td>
    <td align="left">
    <td align="left"></td>
  </tr>
  <tr>
    <td colspan=3>This computes the Dixmier-Ohno invariants of a
    plane quartic (given as a homogeneous polynomial in three
    variables) and the Shioda invariants of a genus 3 hyperelliptic
    (see Shioda, <i>On the graded ring of invariants of binary octavics</i>).
    </td>
  </tr>
  <tr>
    <td><b>Cryptosystems</b></td>
    <td align="left">
    <td align="left"></td>
  <tr>
    <td colspan=3>
    This is a teaching package for use in a course in classical cryptography,
    covering substitution and transposition ciphers, linear feedback shift
    registers, RSA, and ElGamal.
    See my former <a href="http://iml.univ-mrs.fr/~kohel/alg/../tch/USyd/MATH3024/index.html">MATH3024</a>, which
    contains information on its use (particularly the tutorials), but see
    the course page for my ICE-EM/AMSI Summer School course in
    <a href="http://iml.univ-mrs.fr/~kohel/alg/../tch/Crypto/index.html">Cryptography</a> for my book and an
    expanded cryptography package in <a href="http://www.sagemath.org/">Sage</a>.
    </td>
  </tr>
  <tr>
    <td><b>User Databases</b></td>
    <td align="left"><a href="http://iml.univ-mrs.fr/~kohel/alg/doc/DBUser.txt">DBUser.txt</a></td>
  </tr>
  <tr>
    <td colspan=3>This package provides an interface to the various databases on the
    <a href="http://iml.univ-mrs.fr/~kohel/alg/../dbs/index.html">Echidna Databases</a> page.
  </tr>
</table>

<hr noshade size=2>

This page hosts links to code and documentation in areas related to research in number theory
and arithmetic geometry developed in association with research in this area, and made available
under the <b>GNU Public License</b> version 2 or higher (see <a href="GPL.txt">GPL</a>)
and the <b>GNU Free Documentation License</b> (see <a href="FDL.txt">FDL</a>), respectively.
They are made available in the spirit of open academic exchange of ideas and advancing research.
To use code developed in Magma you will need a copy of
<a href="http://magma.maths.usyd.edu.au">Magma</a>. The algorithms represented here build on
thesis work at <a href="http://www.math.berkeley.edu">The University of California, Berkeley</a>,
and subsequent postdoctoral research at the
<a href="http://www.math.nus.edu.sg">National University of Singapore</a>, the
<a href="http://www.msri.org">Mathematical Sciences Research Institute</a> (Berkeley), the
<a href="http://www.maths.usyd.edu.au">University of Sydney</a>, and the
<a href="http://www.i2m.univ-amu.fr">Institut de Math&eacute;matiques de Marseille</a>,
with contributions and inspiration from many collaborators (see above).

<hr noshade size=2>
<table>
<tr>
  <td width="95%">
    <address>
      David Kohel
      (<a href="mailto:David.Kohel@univ-amu.fr">David.Kohel@univ-amu.fr</a>)
      Institut de Math&eacute;matiques de Marseille
    </address>
  </td>
  <td width="5%">
    <a href="http://validator.w3.org/check/referer">
    <img border="0" src="http://www.w3.org/Icons/valid-html40" alt="Valid HTML 4.0!" height="31" width="88"></a>
  </td>
</tr>
</table>


Theory vfmTest2537[no_sig_docs]
Ancestors vfmTestDefs2537
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2537_0.nsv"];
val thyn = "vfmTestDefs2537";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

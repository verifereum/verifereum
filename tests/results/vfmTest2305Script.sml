Theory vfmTest2305[no_sig_docs]
Ancestors vfmTestDefs2305
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2305_0.nsv"];
val thyn = "vfmTestDefs2305";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

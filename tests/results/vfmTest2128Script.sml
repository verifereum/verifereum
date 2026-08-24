Theory vfmTest2128[no_sig_docs]
Ancestors vfmTestDefs2128
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2128_0.nsv"];
val thyn = "vfmTestDefs2128";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

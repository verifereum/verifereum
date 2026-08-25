Theory vfmTest2168[no_sig_docs]
Ancestors vfmTestDefs2168
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2168_0.nsv"];
val thyn = "vfmTestDefs2168";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

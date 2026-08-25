Theory vfmTest2767[no_sig_docs]
Ancestors vfmTestDefs2767
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2767_0.nsv", "result2767_1.nsv", "result2767_2.nsv", "result2767_3.nsv"];
val thyn = "vfmTestDefs2767";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

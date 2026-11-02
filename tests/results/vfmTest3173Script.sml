Theory vfmTest3173[no_sig_docs]
Ancestors vfmTestDefs3173
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3173_0.nsv", "result3173_1.nsv"];
val thyn = "vfmTestDefs3173";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

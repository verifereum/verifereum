Theory vfmTest0310[no_sig_docs]
Ancestors vfmTestDefs0310
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0310_0.nsv", "result0310_1.nsv"];
val thyn = "vfmTestDefs0310";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

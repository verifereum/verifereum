Theory vfmTest3089[no_sig_docs]
Ancestors vfmTestDefs3089
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3089_0.nsv", "result3089_1.nsv"];
val thyn = "vfmTestDefs3089";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

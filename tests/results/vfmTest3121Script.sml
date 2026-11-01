Theory vfmTest3121[no_sig_docs]
Ancestors vfmTestDefs3121
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3121_0.nsv", "result3121_1.nsv"];
val thyn = "vfmTestDefs3121";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

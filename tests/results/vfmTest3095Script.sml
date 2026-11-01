Theory vfmTest3095[no_sig_docs]
Ancestors vfmTestDefs3095
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3095_0.nsv", "result3095_1.nsv"];
val thyn = "vfmTestDefs3095";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest3109[no_sig_docs]
Ancestors vfmTestDefs3109
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3109_0.nsv", "result3109_1.nsv"];
val thyn = "vfmTestDefs3109";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

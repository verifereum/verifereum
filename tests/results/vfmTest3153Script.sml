Theory vfmTest3153[no_sig_docs]
Ancestors vfmTestDefs3153
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3153_0.nsv", "result3153_1.nsv", "result3153_2.nsv", "result3153_3.nsv"];
val thyn = "vfmTestDefs3153";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

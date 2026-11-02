Theory vfmTest3049[no_sig_docs]
Ancestors vfmTestDefs3049
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3049_0.nsv", "result3049_1.nsv", "result3049_2.nsv", "result3049_3.nsv", "result3049_4.nsv", "result3049_5.nsv"];
val thyn = "vfmTestDefs3049";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

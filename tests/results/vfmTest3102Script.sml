Theory vfmTest3102[no_sig_docs]
Ancestors vfmTestDefs3102
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3102_0.nsv", "result3102_1.nsv", "result3102_2.nsv", "result3102_3.nsv", "result3102_4.nsv", "result3102_5.nsv", "result3102_6.nsv", "result3102_7.nsv"];
val thyn = "vfmTestDefs3102";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

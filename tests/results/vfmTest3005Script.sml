Theory vfmTest3005[no_sig_docs]
Ancestors vfmTestDefs3005
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3005_0.nsv", "result3005_1.nsv", "result3005_2.nsv", "result3005_3.nsv", "result3005_4.nsv", "result3005_5.nsv", "result3005_6.nsv", "result3005_7.nsv"];
val thyn = "vfmTestDefs3005";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0245[no_sig_docs]
Ancestors vfmTestDefs0245
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0245_0.nsv", "result0245_1.nsv", "result0245_2.nsv", "result0245_3.nsv", "result0245_4.nsv", "result0245_5.nsv", "result0245_6.nsv", "result0245_7.nsv", "result0245_8.nsv", "result0245_9.nsv", "result0245_10.nsv", "result0245_11.nsv", "result0245_12.nsv", "result0245_13.nsv"];
val thyn = "vfmTestDefs0245";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

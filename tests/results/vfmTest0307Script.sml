Theory vfmTest0307[no_sig_docs]
Ancestors vfmTestDefs0307
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0307_0.nsv", "result0307_1.nsv", "result0307_2.nsv", "result0307_3.nsv", "result0307_4.nsv", "result0307_5.nsv", "result0307_6.nsv", "result0307_7.nsv", "result0307_8.nsv", "result0307_9.nsv", "result0307_10.nsv", "result0307_11.nsv", "result0307_12.nsv", "result0307_13.nsv", "result0307_14.nsv", "result0307_15.nsv", "result0307_16.nsv"];
val thyn = "vfmTestDefs0307";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

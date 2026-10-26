Theory vfmTest1345[no_sig_docs]
Ancestors vfmTestDefs1345
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1345_0.nsv", "result1345_1.nsv", "result1345_2.nsv", "result1345_3.nsv", "result1345_4.nsv", "result1345_5.nsv", "result1345_6.nsv", "result1345_7.nsv", "result1345_8.nsv", "result1345_9.nsv", "result1345_10.nsv", "result1345_11.nsv", "result1345_12.nsv", "result1345_13.nsv", "result1345_14.nsv", "result1345_15.nsv", "result1345_16.nsv", "result1345_17.nsv", "result1345_18.nsv", "result1345_19.nsv", "result1345_20.nsv", "result1345_21.nsv", "result1345_22.nsv", "result1345_23.nsv"];
val thyn = "vfmTestDefs1345";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

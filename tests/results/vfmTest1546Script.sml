Theory vfmTest1546[no_sig_docs]
Ancestors vfmTestDefs1546
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1546_0.nsv", "result1546_1.nsv", "result1546_2.nsv", "result1546_3.nsv", "result1546_4.nsv", "result1546_5.nsv", "result1546_6.nsv", "result1546_7.nsv", "result1546_8.nsv", "result1546_9.nsv", "result1546_10.nsv", "result1546_11.nsv", "result1546_12.nsv", "result1546_13.nsv", "result1546_14.nsv", "result1546_15.nsv", "result1546_16.nsv", "result1546_17.nsv", "result1546_18.nsv", "result1546_19.nsv"];
val thyn = "vfmTestDefs1546";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

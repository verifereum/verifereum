Theory vfmTest2196[no_sig_docs]
Ancestors vfmTestDefs2196
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2196_0.nsv", "result2196_1.nsv", "result2196_2.nsv", "result2196_3.nsv", "result2196_4.nsv", "result2196_5.nsv", "result2196_6.nsv", "result2196_7.nsv", "result2196_8.nsv", "result2196_9.nsv", "result2196_10.nsv", "result2196_11.nsv", "result2196_12.nsv", "result2196_13.nsv", "result2196_14.nsv", "result2196_15.nsv", "result2196_16.nsv", "result2196_17.nsv", "result2196_18.nsv", "result2196_19.nsv", "result2196_20.nsv", "result2196_21.nsv", "result2196_22.nsv", "result2196_23.nsv"];
val thyn = "vfmTestDefs2196";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

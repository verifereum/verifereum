Theory vfmTest0703[no_sig_docs]
Ancestors vfmTestDefs0703
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0703_0.nsv", "result0703_1.nsv", "result0703_2.nsv", "result0703_3.nsv", "result0703_4.nsv", "result0703_5.nsv", "result0703_6.nsv", "result0703_7.nsv", "result0703_8.nsv", "result0703_9.nsv", "result0703_10.nsv", "result0703_11.nsv", "result0703_12.nsv", "result0703_13.nsv", "result0703_14.nsv", "result0703_15.nsv", "result0703_16.nsv", "result0703_17.nsv", "result0703_18.nsv", "result0703_19.nsv", "result0703_20.nsv", "result0703_21.nsv", "result0703_22.nsv", "result0703_23.nsv"];
val thyn = "vfmTestDefs0703";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

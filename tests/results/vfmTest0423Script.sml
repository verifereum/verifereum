Theory vfmTest0423[no_sig_docs]
Ancestors vfmTestDefs0423
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0423_0.nsv", "result0423_1.nsv", "result0423_2.nsv", "result0423_3.nsv", "result0423_4.nsv", "result0423_5.nsv", "result0423_6.nsv", "result0423_7.nsv", "result0423_8.nsv", "result0423_9.nsv", "result0423_10.nsv", "result0423_11.nsv", "result0423_12.nsv", "result0423_13.nsv", "result0423_14.nsv", "result0423_15.nsv", "result0423_16.nsv", "result0423_17.nsv", "result0423_18.nsv", "result0423_19.nsv", "result0423_20.nsv", "result0423_21.nsv", "result0423_22.nsv", "result0423_23.nsv", "result0423_24.nsv", "result0423_25.nsv", "result0423_26.nsv"];
val thyn = "vfmTestDefs0423";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

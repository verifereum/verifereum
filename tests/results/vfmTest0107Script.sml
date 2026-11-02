Theory vfmTest0107[no_sig_docs]
Ancestors vfmTestDefs0107
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0107_0.nsv", "result0107_1.nsv", "result0107_2.nsv", "result0107_3.nsv", "result0107_4.nsv", "result0107_5.nsv", "result0107_6.nsv", "result0107_7.nsv", "result0107_8.nsv", "result0107_9.nsv", "result0107_10.nsv", "result0107_11.nsv", "result0107_12.nsv", "result0107_13.nsv", "result0107_14.nsv", "result0107_15.nsv", "result0107_16.nsv", "result0107_17.nsv", "result0107_18.nsv", "result0107_19.nsv", "result0107_20.nsv", "result0107_21.nsv", "result0107_22.nsv", "result0107_23.nsv", "result0107_24.nsv"];
val thyn = "vfmTestDefs0107";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0045[no_sig_docs]
Ancestors vfmTestDefs0045
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0045_0.nsv", "result0045_1.nsv", "result0045_2.nsv", "result0045_3.nsv", "result0045_4.nsv", "result0045_5.nsv", "result0045_6.nsv", "result0045_7.nsv", "result0045_8.nsv", "result0045_9.nsv", "result0045_10.nsv", "result0045_11.nsv", "result0045_12.nsv", "result0045_13.nsv", "result0045_14.nsv", "result0045_15.nsv", "result0045_16.nsv", "result0045_17.nsv", "result0045_18.nsv", "result0045_19.nsv", "result0045_20.nsv", "result0045_21.nsv", "result0045_22.nsv", "result0045_23.nsv"];
val thyn = "vfmTestDefs0045";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

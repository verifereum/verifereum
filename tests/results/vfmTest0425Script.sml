Theory vfmTest0425[no_sig_docs]
Ancestors vfmTestDefs0425
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0425_0.nsv", "result0425_1.nsv", "result0425_2.nsv", "result0425_3.nsv", "result0425_4.nsv", "result0425_5.nsv", "result0425_6.nsv", "result0425_7.nsv", "result0425_8.nsv", "result0425_9.nsv", "result0425_10.nsv", "result0425_11.nsv", "result0425_12.nsv", "result0425_13.nsv", "result0425_14.nsv", "result0425_15.nsv", "result0425_16.nsv", "result0425_17.nsv", "result0425_18.nsv", "result0425_19.nsv", "result0425_20.nsv", "result0425_21.nsv", "result0425_22.nsv", "result0425_23.nsv", "result0425_24.nsv", "result0425_25.nsv", "result0425_26.nsv"];
val thyn = "vfmTestDefs0425";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0673[no_sig_docs]
Ancestors vfmTestDefs0673
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0673_0.nsv", "result0673_1.nsv", "result0673_2.nsv", "result0673_3.nsv", "result0673_4.nsv", "result0673_5.nsv", "result0673_6.nsv", "result0673_7.nsv", "result0673_8.nsv", "result0673_9.nsv", "result0673_10.nsv", "result0673_11.nsv", "result0673_12.nsv", "result0673_13.nsv", "result0673_14.nsv", "result0673_15.nsv", "result0673_16.nsv", "result0673_17.nsv", "result0673_18.nsv", "result0673_19.nsv", "result0673_20.nsv", "result0673_21.nsv"];
val thyn = "vfmTestDefs0673";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

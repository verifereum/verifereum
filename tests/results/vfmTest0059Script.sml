Theory vfmTest0059[no_sig_docs]
Ancestors vfmTestDefs0059
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0059_0.nsv", "result0059_1.nsv", "result0059_2.nsv", "result0059_3.nsv", "result0059_4.nsv", "result0059_5.nsv", "result0059_6.nsv", "result0059_7.nsv", "result0059_8.nsv", "result0059_9.nsv", "result0059_10.nsv", "result0059_11.nsv", "result0059_12.nsv", "result0059_13.nsv", "result0059_14.nsv", "result0059_15.nsv", "result0059_16.nsv", "result0059_17.nsv", "result0059_18.nsv", "result0059_19.nsv", "result0059_20.nsv", "result0059_21.nsv", "result0059_22.nsv", "result0059_23.nsv"];
val thyn = "vfmTestDefs0059";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

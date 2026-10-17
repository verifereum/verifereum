Theory vfmTest0672[no_sig_docs]
Ancestors vfmTestDefs0672
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0672_0.nsv", "result0672_1.nsv", "result0672_2.nsv", "result0672_3.nsv", "result0672_4.nsv", "result0672_5.nsv", "result0672_6.nsv", "result0672_7.nsv", "result0672_8.nsv", "result0672_9.nsv", "result0672_10.nsv", "result0672_11.nsv", "result0672_12.nsv", "result0672_13.nsv", "result0672_14.nsv", "result0672_15.nsv", "result0672_16.nsv", "result0672_17.nsv", "result0672_18.nsv", "result0672_19.nsv", "result0672_20.nsv", "result0672_21.nsv", "result0672_22.nsv", "result0672_23.nsv"];
val thyn = "vfmTestDefs0672";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

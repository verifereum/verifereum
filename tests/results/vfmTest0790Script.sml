Theory vfmTest0790[no_sig_docs]
Ancestors vfmTestDefs0790
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0790_0.nsv", "result0790_1.nsv", "result0790_2.nsv", "result0790_3.nsv", "result0790_4.nsv", "result0790_5.nsv", "result0790_6.nsv", "result0790_7.nsv", "result0790_8.nsv", "result0790_9.nsv", "result0790_10.nsv", "result0790_11.nsv", "result0790_12.nsv", "result0790_13.nsv", "result0790_14.nsv", "result0790_15.nsv", "result0790_16.nsv", "result0790_17.nsv", "result0790_18.nsv", "result0790_19.nsv", "result0790_20.nsv", "result0790_21.nsv", "result0790_22.nsv", "result0790_23.nsv"];
val thyn = "vfmTestDefs0790";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

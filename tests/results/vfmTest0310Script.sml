Theory vfmTest0310[no_sig_docs]
Ancestors vfmTestDefs0310
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0310_0.nsv", "result0310_1.nsv", "result0310_2.nsv", "result0310_3.nsv", "result0310_4.nsv", "result0310_5.nsv", "result0310_6.nsv", "result0310_7.nsv", "result0310_8.nsv", "result0310_9.nsv", "result0310_10.nsv", "result0310_11.nsv", "result0310_12.nsv", "result0310_13.nsv", "result0310_14.nsv", "result0310_15.nsv", "result0310_16.nsv", "result0310_17.nsv", "result0310_18.nsv", "result0310_19.nsv", "result0310_20.nsv", "result0310_21.nsv", "result0310_22.nsv", "result0310_23.nsv"];
val thyn = "vfmTestDefs0310";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

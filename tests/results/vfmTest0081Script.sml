Theory vfmTest0081[no_sig_docs]
Ancestors vfmTestDefs0081
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0081_0.nsv", "result0081_1.nsv", "result0081_2.nsv", "result0081_3.nsv", "result0081_4.nsv", "result0081_5.nsv", "result0081_6.nsv", "result0081_7.nsv", "result0081_8.nsv", "result0081_9.nsv", "result0081_10.nsv", "result0081_11.nsv", "result0081_12.nsv", "result0081_13.nsv", "result0081_14.nsv", "result0081_15.nsv", "result0081_16.nsv", "result0081_17.nsv", "result0081_18.nsv", "result0081_19.nsv", "result0081_20.nsv", "result0081_21.nsv", "result0081_22.nsv", "result0081_23.nsv"];
val thyn = "vfmTestDefs0081";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

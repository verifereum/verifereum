Theory vfmTest0061[no_sig_docs]
Ancestors vfmTestDefs0061
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0061_0.nsv", "result0061_1.nsv", "result0061_2.nsv", "result0061_3.nsv", "result0061_4.nsv", "result0061_5.nsv", "result0061_6.nsv", "result0061_7.nsv", "result0061_8.nsv", "result0061_9.nsv", "result0061_10.nsv", "result0061_11.nsv", "result0061_12.nsv", "result0061_13.nsv", "result0061_14.nsv", "result0061_15.nsv", "result0061_16.nsv", "result0061_17.nsv", "result0061_18.nsv", "result0061_19.nsv", "result0061_20.nsv", "result0061_21.nsv", "result0061_22.nsv", "result0061_23.nsv"];
val thyn = "vfmTestDefs0061";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

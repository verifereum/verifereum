Theory vfmTest0010[no_sig_docs]
Ancestors vfmTestDefs0010
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0010_0.nsv", "result0010_1.nsv", "result0010_2.nsv", "result0010_3.nsv", "result0010_4.nsv", "result0010_5.nsv", "result0010_6.nsv", "result0010_7.nsv", "result0010_8.nsv", "result0010_9.nsv", "result0010_10.nsv", "result0010_11.nsv", "result0010_12.nsv", "result0010_13.nsv", "result0010_14.nsv", "result0010_15.nsv", "result0010_16.nsv", "result0010_17.nsv", "result0010_18.nsv", "result0010_19.nsv", "result0010_20.nsv", "result0010_21.nsv", "result0010_22.nsv", "result0010_23.nsv"];
val thyn = "vfmTestDefs0010";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

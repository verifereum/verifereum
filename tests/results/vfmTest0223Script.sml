Theory vfmTest0223[no_sig_docs]
Ancestors vfmTestDefs0223
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0223_0.nsv", "result0223_1.nsv", "result0223_2.nsv", "result0223_3.nsv", "result0223_4.nsv", "result0223_5.nsv", "result0223_6.nsv", "result0223_7.nsv", "result0223_8.nsv", "result0223_9.nsv", "result0223_10.nsv", "result0223_11.nsv", "result0223_12.nsv", "result0223_13.nsv", "result0223_14.nsv", "result0223_15.nsv", "result0223_16.nsv", "result0223_17.nsv", "result0223_18.nsv", "result0223_19.nsv", "result0223_20.nsv", "result0223_21.nsv"];
val thyn = "vfmTestDefs0223";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

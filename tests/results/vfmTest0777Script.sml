Theory vfmTest0777[no_sig_docs]
Ancestors vfmTestDefs0777
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0777_0.nsv", "result0777_1.nsv", "result0777_2.nsv", "result0777_3.nsv", "result0777_4.nsv", "result0777_5.nsv", "result0777_6.nsv", "result0777_7.nsv", "result0777_8.nsv", "result0777_9.nsv", "result0777_10.nsv", "result0777_11.nsv", "result0777_12.nsv", "result0777_13.nsv", "result0777_14.nsv", "result0777_15.nsv", "result0777_16.nsv", "result0777_17.nsv", "result0777_18.nsv", "result0777_19.nsv"];
val thyn = "vfmTestDefs0777";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

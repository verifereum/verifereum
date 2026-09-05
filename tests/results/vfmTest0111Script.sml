Theory vfmTest0111[no_sig_docs]
Ancestors vfmTestDefs0111
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0111_0.nsv", "result0111_1.nsv", "result0111_2.nsv", "result0111_3.nsv", "result0111_4.nsv", "result0111_5.nsv", "result0111_6.nsv", "result0111_7.nsv", "result0111_8.nsv", "result0111_9.nsv", "result0111_10.nsv", "result0111_11.nsv", "result0111_12.nsv", "result0111_13.nsv", "result0111_14.nsv", "result0111_15.nsv", "result0111_16.nsv", "result0111_17.nsv", "result0111_18.nsv", "result0111_19.nsv", "result0111_20.nsv"];
val thyn = "vfmTestDefs0111";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

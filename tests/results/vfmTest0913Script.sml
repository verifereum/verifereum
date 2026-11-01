Theory vfmTest0913[no_sig_docs]
Ancestors vfmTestDefs0913
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0913_0.nsv", "result0913_1.nsv", "result0913_2.nsv", "result0913_3.nsv", "result0913_4.nsv", "result0913_5.nsv", "result0913_6.nsv", "result0913_7.nsv", "result0913_8.nsv", "result0913_9.nsv", "result0913_10.nsv", "result0913_11.nsv", "result0913_12.nsv", "result0913_13.nsv", "result0913_14.nsv", "result0913_15.nsv", "result0913_16.nsv", "result0913_17.nsv", "result0913_18.nsv", "result0913_19.nsv", "result0913_20.nsv", "result0913_21.nsv", "result0913_22.nsv", "result0913_23.nsv"];
val thyn = "vfmTestDefs0913";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

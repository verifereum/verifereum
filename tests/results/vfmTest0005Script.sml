Theory vfmTest0005[no_sig_docs]
Ancestors vfmTestDefs0005
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0005_0.nsv", "result0005_1.nsv", "result0005_2.nsv", "result0005_3.nsv", "result0005_4.nsv", "result0005_5.nsv", "result0005_6.nsv", "result0005_7.nsv", "result0005_8.nsv", "result0005_9.nsv", "result0005_10.nsv", "result0005_11.nsv", "result0005_12.nsv", "result0005_13.nsv", "result0005_14.nsv", "result0005_15.nsv", "result0005_16.nsv", "result0005_17.nsv", "result0005_18.nsv", "result0005_19.nsv", "result0005_20.nsv", "result0005_21.nsv", "result0005_22.nsv", "result0005_23.nsv"];
val thyn = "vfmTestDefs0005";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0500[no_sig_docs]
Ancestors vfmTestDefs0500
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0500_0.nsv", "result0500_1.nsv", "result0500_2.nsv", "result0500_3.nsv", "result0500_4.nsv", "result0500_5.nsv", "result0500_6.nsv", "result0500_7.nsv", "result0500_8.nsv", "result0500_9.nsv", "result0500_10.nsv", "result0500_11.nsv", "result0500_12.nsv", "result0500_13.nsv", "result0500_14.nsv", "result0500_15.nsv", "result0500_16.nsv", "result0500_17.nsv", "result0500_18.nsv", "result0500_19.nsv", "result0500_20.nsv", "result0500_21.nsv", "result0500_22.nsv", "result0500_23.nsv"];
val thyn = "vfmTestDefs0500";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

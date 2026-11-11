Theory vfmTest0419[no_sig_docs]
Ancestors vfmTestDefs0419
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0419_0.nsv", "result0419_1.nsv", "result0419_2.nsv", "result0419_3.nsv", "result0419_4.nsv", "result0419_5.nsv", "result0419_6.nsv", "result0419_7.nsv", "result0419_8.nsv", "result0419_9.nsv", "result0419_10.nsv", "result0419_11.nsv", "result0419_12.nsv", "result0419_13.nsv", "result0419_14.nsv", "result0419_15.nsv", "result0419_16.nsv", "result0419_17.nsv", "result0419_18.nsv", "result0419_19.nsv", "result0419_20.nsv", "result0419_21.nsv", "result0419_22.nsv", "result0419_23.nsv", "result0419_24.nsv", "result0419_25.nsv", "result0419_26.nsv"];
val thyn = "vfmTestDefs0419";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0682[no_sig_docs]
Ancestors vfmTestDefs0682
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0682_0.nsv", "result0682_1.nsv", "result0682_2.nsv", "result0682_3.nsv", "result0682_4.nsv", "result0682_5.nsv", "result0682_6.nsv", "result0682_7.nsv", "result0682_8.nsv", "result0682_9.nsv", "result0682_10.nsv", "result0682_11.nsv", "result0682_12.nsv", "result0682_13.nsv", "result0682_14.nsv", "result0682_15.nsv", "result0682_16.nsv", "result0682_17.nsv", "result0682_18.nsv", "result0682_19.nsv", "result0682_20.nsv", "result0682_21.nsv", "result0682_22.nsv", "result0682_23.nsv"];
val thyn = "vfmTestDefs0682";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

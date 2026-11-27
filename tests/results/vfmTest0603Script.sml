Theory vfmTest0603[no_sig_docs]
Ancestors vfmTestDefs0603
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0603_0.nsv", "result0603_1.nsv", "result0603_2.nsv", "result0603_3.nsv", "result0603_4.nsv", "result0603_5.nsv", "result0603_6.nsv", "result0603_7.nsv", "result0603_8.nsv", "result0603_9.nsv", "result0603_10.nsv", "result0603_11.nsv", "result0603_12.nsv", "result0603_13.nsv", "result0603_14.nsv", "result0603_15.nsv", "result0603_16.nsv", "result0603_17.nsv", "result0603_18.nsv", "result0603_19.nsv", "result0603_20.nsv", "result0603_21.nsv", "result0603_22.nsv", "result0603_23.nsv"];
val thyn = "vfmTestDefs0603";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

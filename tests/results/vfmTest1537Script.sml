Theory vfmTest1537[no_sig_docs]
Ancestors vfmTestDefs1537
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1537_0.nsv", "result1537_1.nsv", "result1537_2.nsv", "result1537_3.nsv", "result1537_4.nsv", "result1537_5.nsv", "result1537_6.nsv", "result1537_7.nsv", "result1537_8.nsv", "result1537_9.nsv", "result1537_10.nsv", "result1537_11.nsv", "result1537_12.nsv", "result1537_13.nsv", "result1537_14.nsv", "result1537_15.nsv", "result1537_16.nsv", "result1537_17.nsv", "result1537_18.nsv", "result1537_19.nsv"];
val thyn = "vfmTestDefs1537";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

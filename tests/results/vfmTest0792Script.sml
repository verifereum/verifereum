Theory vfmTest0792[no_sig_docs]
Ancestors vfmTestDefs0792
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0792_0.nsv", "result0792_1.nsv", "result0792_2.nsv", "result0792_3.nsv", "result0792_4.nsv", "result0792_5.nsv", "result0792_6.nsv", "result0792_7.nsv", "result0792_8.nsv", "result0792_9.nsv", "result0792_10.nsv", "result0792_11.nsv"];
val thyn = "vfmTestDefs0792";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

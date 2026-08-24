Theory vfmTest0042[no_sig_docs]
Ancestors vfmTestDefs0042
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0042_0.nsv", "result0042_1.nsv", "result0042_2.nsv", "result0042_3.nsv", "result0042_4.nsv", "result0042_5.nsv", "result0042_6.nsv", "result0042_7.nsv", "result0042_8.nsv"];
val thyn = "vfmTestDefs0042";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
